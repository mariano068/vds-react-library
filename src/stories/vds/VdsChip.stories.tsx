import { storiesOf } from '@storybook/react';
import React from 'react';
import { muiTheme } from 'storybook-addon-material-ui5';
import { version } from '../../../package.json';
import CodeHighlight from '../shared/CodeHighlight';
import { Highlight } from '../shared/Highlight';
import { BaseStoryLayout } from '../shared/StoryLayouts';
import { Default_Chip_Example, default_chip_snippet } from '../snippets/VdsChip.snippets';

const storyTitle = 'Chip';

storiesOf(`vds@${version}`, module)
  .addDecorator(muiTheme())
  .add(storyTitle, () => (
    <BaseStoryLayout storyTitle={storyTitle}>
      <p>Chip is a compact element that represent an input, attribute, or action.</p>
      <h3>Multiselect/Autocomplete Chip</h3>
      <CodeHighlight>
        <Default_Chip_Example />
      </CodeHighlight>
      <h3>Code</h3>
      <Highlight language='typescript'>{default_chip_snippet}</Highlight>
    </BaseStoryLayout>
  ));
