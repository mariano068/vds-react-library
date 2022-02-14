import { storiesOf } from '@storybook/react';
import React from 'react';
import { muiTheme } from 'storybook-addon-material-ui5';
import { version } from '../../../package.json';
import CodeHighlight from '../shared/CodeHighlight';
import { Highlight } from '../shared/Highlight';
import { BaseStoryLayout } from '../shared/StoryLayouts';
import { Breadcrumb_Default_Example, breadcrumb_Default_Example_snippet } from '../snippets/VdsBreadcrumb.snippets';

const storyTitle = 'Breadcrumb';

storiesOf(`vds@${version}`, module)
  .addDecorator(muiTheme())
  .add(storyTitle, () => (
    <BaseStoryLayout storyTitle={storyTitle}>
      <p>Breadcrumb is used to show the path of a page. This element allows the user to always know where he/she is.</p>
      <h3>Overview</h3>
      <p>Breadcrumb improves state control and helps the user navigation increasing findability through pages. It's normally placed on top of the page close to the title line.</p>
      <CodeHighlight>
        <Breadcrumb_Default_Example />
      </CodeHighlight>
      <h3>Code</h3>
      <Highlight language='typescript'>{breadcrumb_Default_Example_snippet}</Highlight>
    </BaseStoryLayout>
  ));
