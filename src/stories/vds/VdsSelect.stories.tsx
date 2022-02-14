import { storiesOf } from '@storybook/react';
import React from 'react';
import { muiTheme } from 'storybook-addon-material-ui5';
import { version } from '../../../package.json';
import CodeHighlight from '../shared/CodeHighlight';
import { Highlight } from '../shared/Highlight';
import { BaseStoryLayout } from '../shared/StoryLayouts';
import { SingleSelection_Example, singleSelection_example_snippet } from '../snippets/VdsSelect.snippets';

const storyTitle = 'Selects';

storiesOf(`vds@${version}`, module)
  .addDecorator(muiTheme())
  .add(storyTitle, () => (
    <BaseStoryLayout storyTitle={storyTitle}>
      <p>
        Select is a type of input that is used in long forms. The user can submit data by choosing one or more options from a pre-determined list.
      </p>
      <h3>Overview</h3>
      <p>
        Selection controls allow the user to select one or multiple options, and confirming choices and actions. Selection controls are used when users need to make decisions or declare preferences.
      </p>
      <h3>Single selection</h3>
      <CodeHighlight>
        <SingleSelection_Example />
      </CodeHighlight>
      <h3>Code</h3>
      <Highlight language='typescript'>{singleSelection_example_snippet}</Highlight>
    </BaseStoryLayout>
  ));
