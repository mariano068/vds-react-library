import { storiesOf } from '@storybook/react';
import React from 'react';
import { muiTheme } from 'storybook-addon-material-ui5';
import { version } from '../../../package.json';
import CodeHighlight from '../shared/CodeHighlight';
import { Highlight } from '../shared/Highlight';
import { BaseStoryLayout } from '../shared/StoryLayouts';
import { Standard_Example, standard_example_snippet } from '../snippets/VdsTextField.snippets';

const storyTitle = 'Text Fields';

storiesOf(`vds@${version}`, module)
  .addDecorator(muiTheme())
  .add(storyTitle, () => (
    <BaseStoryLayout storyTitle={storyTitle}>
      <p>
        Input fields enable users to enter or edit text into a UI. They typically appear in forms and dialogs.
      </p>
      <h3>Overview</h3>
      <p>
        Input fields allow users to interact with and input data into the user interface. They should stand out and indicate that users can input information, providing a clear affordance for interaction, and making the fields discoverable in layouts.
      </p>
      <h3>Kind & variants</h3>
      <CodeHighlight>
        <Standard_Example />
      </CodeHighlight>
      <h3>Code</h3>
      <Highlight language='typescript'>{standard_example_snippet}</Highlight>
    </BaseStoryLayout>
  ));
